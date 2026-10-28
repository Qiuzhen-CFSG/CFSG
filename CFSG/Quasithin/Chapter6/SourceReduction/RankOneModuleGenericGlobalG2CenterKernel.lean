module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalSpecialCenterAction
public import Theory.SpecificGroups.PSL2.BorelActorInner
public import Theory.GroupTheory.PCoreNormalizerAction
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalG2Nonfusion

/-!
# Removing the original LT-core in the compatible G₂ comparison

Let K = O²(H), S = O₂(N_G(L) ∩ H), and Q = O₂(LT). The actual
left Borel realizes every inner right-Borel action on K/O₂(K). In the
split G₂ model, write a right Borel element as u h(l,m). Multiplying by
h(l⁻¹,l⁻¹) puts it in the left local factor and leaves its right-quotient
action unchanged: this diagonal matrix is scalar on the right null plane.
Both compatible maps and their whole-overlap agreement transport this lift.

The image of Q on K/O₂(K) is a two-group normalized by these Borel
actors and preserving the original quotient Sylow. The binary PSL₂ Borel
actor theorem therefore makes it inner. The previously proved right-field
action kernel then places Q in S. This controls the intrinsic O₂(LT)
directly, without identifying it with the core of the larger parabolic or
assuming that an isolated local automorphism extends to a model automorphism.

Combining Q ≤ S with the original center-fixer bound removes the last
centralizer premise in the marked G₂ nonfusion argument, at all degrees
n > 1, including field order four. Triality and ambient recognition remain
separate obligations. Source: Aschbacher–Smith F.4.29(2,7), pp.289–290,
F.4.35, p.292, and 5.3.3, p.659 (`refs/quasithin.pdf`); the explicit G₂
coordinates come from the licensed ATLAS port imported above.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Atlas.G2 Atlas.G2.Explicit Atlas.G2.LieParabolicSetup Atlas.SplitOctonion
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.G2CoreComparison
variable {F : Type} [Field F] [CharP F 2]

private theorem scalar_torus_quotient (l : Fˣ) (x : local₁ (F := F)) :
    shortSLHom ⟨torus l l * x.val * (torus l l)⁻¹,
      (mem_normalizer_iff.mp (torus_normalizes_local₁ ⟨(l,l),rfl⟩) x.val).mp x.property⟩ =
      shortSLHom x := by
  have ht (a b : Fˣ) :
      shortRepresentation ⟨torus a b,torus_le_shortPlaneStabilizer ⟨(a,b),rfl⟩⟩ =
        !![(a:F),0;0,(b:F)] := by
    ext i j
    change (torus a b).val (basisVector (j.castLE (by decide : 2 ≤ 8)))
      (i.castLE (by decide : 2 ≤ 8)) = _
    fin_cases i <;> fin_cases j <;>
      simp [torus,torusEquiv,torusLinear,torusWeights,basisVector]
  have hinv : (torus l l : Model F)⁻¹ = torus l⁻¹ l⁻¹ :=
    (map_inv torusHom (l,l)).symm
  apply Subtype.ext
  change shortRepresentation ⟨_,_⟩ = shortRepresentation ⟨_,_⟩
  have hxc : torus l l*x.val*(torus l l)⁻¹ ∈ shortPlaneStabilizer (F := F) :=
    (shortPlaneStabilizer (F := F)).mul_mem
      ((shortPlaneStabilizer (F := F)).mul_mem
        (torus_le_shortPlaneStabilizer ⟨(l,l),rfl⟩)
        (parabolic₁_le_shortPlaneStabilizer
          ((le_sup_left.trans_eq (local₁_sup_borel (F := F))) x.property)))
      ((shortPlaneStabilizer (F := F)).inv_mem (torus_le_shortPlaneStabilizer ⟨(l,l),rfl⟩))
  have he : (⟨torus l l*x.val*(torus l l)⁻¹,hxc⟩ : shortPlaneStabilizer (F := F)) =
      ⟨torus l l,torus_le_shortPlaneStabilizer ⟨(l,l),rfl⟩⟩ *
        ⟨x.val, parabolic₁_le_shortPlaneStabilizer ((le_sup_left.trans_eq (local₁_sup_borel (F := F))) x.property)⟩ *
      ⟨torus l⁻¹ l⁻¹,torus_le_shortPlaneStabilizer ⟨(l⁻¹,l⁻¹),rfl⟩⟩ := by
    apply Subtype.ext
    exact congrArg (torus l l*x.val*·) hinv
  rw [he,map_mul,map_mul,ht,ht]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply,Matrix.vecMul,Fin.sum_univ_two,mul_comm,mul_left_comm] <;> rfl

private theorem left_borel_action_lift (g : local₁ (F := F)) (hg : g.val ∈ Atlas.G2.borel) :
    ∃ a : Model F, a ∈ local₂ ∧ ∃ ha : a ∈ Atlas.G2.borel,
      ∀ x : local₁ (F := F),
        shortSLHom (local₁.normalizerMonoidHom
          ⟨a,borel_normalizes_local₁ (F := F) ha⟩ x) =
          shortSLHom (g*x*g⁻¹) := by
  obtain ⟨⟨u,v⟩,he⟩ := borelProductEquiv.surjective ⟨g.val,hg⟩
  have he : (u : Model F)*v.val=g.val := congrArg Subtype.val he
  obtain ⟨⟨l,m⟩,hv⟩ := v.property
  have hve : (v : Model F)=torus l m := hv.symm
  rw [hve] at he
  let c := torus l⁻¹ l⁻¹ (K := F)
  let a := g.val*c
  have hcB : c ∈ Atlas.G2.borel := mem_sup_right ⟨(l⁻¹,l⁻¹),rfl⟩
  have haB : a ∈ Atlas.G2.borel := (Atlas.G2.borel (K := F)).mul_mem hg hcB
  have htc : torus l m*c = torus (1:Fˣ) (m*l⁻¹) := by
    change torusHom (l,m)*torusHom (l⁻¹,l⁻¹)=torusHom (1,m*l⁻¹)
    rw [←map_mul]
    simp only [Prod.mk_mul_mk,mul_inv_cancel]
  have htL : torus (1:Fˣ) (m*l⁻¹) ∈ local₂ := by
    rw [local₂_eq_fixingFirstVector]
    change (torus (1:Fˣ) (m*l⁻¹)).val (basisVector 0)=basisVector 0
    rw [torus_first_basis]
    simp
  have haL : a ∈ local₂ := by
    change g.val*c ∈ local₂
    rw [←he,mul_assoc,htc]
    exact local₂.mul_mem (unipotent_le_local₂ u.property) htL
  refine ⟨a,haL,haB,fun x => ?_⟩
  let y : local₁ (F := F) := local₁.normalizerMonoidHom
    ⟨c,borel_normalizes_local₁ hcB⟩ x
  have hy : shortSLHom y = shortSLHom x := scalar_torus_quotient l⁻¹ x
  have ha : local₁.normalizerMonoidHom ⟨a,borel_normalizes_local₁ haB⟩ x = g*y*g⁻¹ := by
    apply Subtype.ext
    change (g.val*c)*x.val*(g.val*c)⁻¹ = g.val*(c*x.val*c⁻¹)*g.val⁻¹
    group
  rw [ha,map_mul,map_mul,map_inv,hy,map_mul,map_mul,map_inv]

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.G2CoreComparison

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
variable {G : Type*} [Group G] [Finite G]

private theorem Preparation.left_core_le_sourceS_of_borel_action
    {κ : GroupClass} {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H)) (h : Input κ T L W n)
    (hTH : (T : Subgroup G) ≤ H)
    (hS : ∀ i : Fin 2, sourceS L H ≤ ![L,residual H] i)
    {F : Type} [Field F] [Finite F] [CharP F 2]
    (e : (residual H ⧸ pCore 2 (residual H)) ≃* Theory.PSL2.Group F)
    (hlift : ∀ k : residual H, k.val ∈ localBorel T (residual H) →
      ∃ a : normalizer (residual H : Set G), a.val ∈ localBorel T L ∧
        pCoreNormalizerAction 2 (residual H) a =
          MulAut.conj (QuotientGroup.mk' (pCore 2 (residual H)) k)) :
    (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤ sourceS L H := by
  let K := residual H
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  let N := normalizer (K : Set G)
  let f := pCoreNormalizerAction 2 K
  have hQT : Q ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le le_sup_right] using
      pCoreIn_le_sylow (L ⊔ (T : Subgroup G)) (T.subtype le_sup_right)
  have hTN : (T : Subgroup G) ≤ N := hTH.trans (le_normalizer_residual H)
  have hQN : Q ≤ N := hQT.trans hTN
  have hLQ : L ≤ normalizer (Q : Set G) :=
    (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left).trans
      ((L ⊔ (T : Subgroup G)).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))
  let D := (Q.subgroupOf N).map f
  have hD : IsPGroup 2 D := (isPGroup_pCoreIn 2 (L ⊔ (T : Subgroup G))).comap_subtype.map f
  have hPs := d.sylow 1
  change ∃ P : Sylow 2 K, (P : Subgroup K).map K.subtype = sourceS L H ⊓ K at hPs
  obtain ⟨P,hP⟩ := hPs
  have hSK : sourceS L H ≤ K := hS 1
  rw [inf_eq_left.mpr hSK] at hP
  have hP' : (P : Subgroup K) = (T : Subgroup G).subgroupOf K := by
    apply map_injective K.subtype_injective
    rw [hP,subgroupOf_map_subtype]
    exact (d.ordinary_sylow_core_geometry h hTH hS).1 1
  let q := QuotientGroup.mk' (pCore 2 K)
  let Pq := P.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 K))
  have hpre : (Pq : Subgroup (K ⧸ pCore 2 K)).comap q = P := by
    change ((P : Subgroup K).map q).comap q = _
    exact comap_map_eq_self (by
      rw [QuotientGroup.ker_mk']
      exact pCore_isPGroup.le_sylow_of_normal P)
  have hDP : ∀ α ∈ D, (Pq : Subgroup (K ⧸ pCore 2 K)).map α.toMonoidHom = Pq := by
    rintro α ⟨a,ha,rfl⟩
    let b := K.normalizerMonoidHom a
    have hPb : (P : Subgroup K).map b.toMonoidHom = P := by
      apply eq_of_le_of_card_ge
      · rintro _ ⟨x,hx,rfl⟩
        rw [hP'] at hx ⊢
        exact (T : Subgroup G).mul_mem ((T : Subgroup G).mul_mem (hQT ha) hx)
          ((T : Subgroup G).inv_mem (hQT ha))
      · rw [card_map_of_injective (f := b.toMonoidHom) b.injective]
    have hc : (f a).toMonoidHom.comp q = q.comp b.toMonoidHom := by
      ext x
      exact pCoreNormalizerAction_mk 2 K a x
    change ((P : Subgroup K).map q).map (f a).toMonoidHom = _
    rw [map_map,hc,←map_map,hPb]
    rfl
  have hBD : (normalizer (Pq : Set (K ⧸ pCore 2 K))).map MulAut.conj ≤
      normalizer (D : Set (MulAut (K ⧸ pCore 2 K))) := by
    rintro _ ⟨x,hx,rfl⟩
    obtain ⟨k,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 K) x
    have hn : (normalizer (Pq : Set (K ⧸ pCore 2 K))).comap q =
        normalizer (P : Set K) := by
      change (normalizer ((Pq : Subgroup (K ⧸ pCore 2 K)) : Set _)).comap q = _
      rw [comap_normalizer_eq_of_surjective _ (QuotientGroup.mk'_surjective _),hpre]
      rfl
    have hk : k ∈ normalizer (P : Set K) := hn ▸ hx
    have hkB : k.val ∈ localBorel T K := by
      rw [localBorel_eq_map]
      exact mem_map_of_mem K.subtype (hP' ▸ hk)
    obtain ⟨a,ha,hea⟩ := hlift k hkB
    rw [←hea]
    apply (le_normalizer_map f)
    apply mem_map_of_mem f
    apply mem_normalizer_iff.mpr
    intro y
    change y.val ∈ Q ↔ a.val*y.val*a.val⁻¹ ∈ Q
    exact mem_normalizer_iff.mp (hLQ ha.1) y.val
  have hinner : D ≤ MulAut.innerSubgroup (K ⧸ pCore 2 K) :=
    Theory.PSL2.borelActorInner_of_mulEquiv F e Pq D hDP hBD (hD.to_le inf_le_left)
  intro t ht
  have hti := hinner (mem_map_of_mem f (show (⟨t,hQN ht⟩ : N) ∈ Q.subgroupOf N from ht))
  have hk : (⟨t,hQT ht⟩ : T) ∈ (residualSylowFieldAction hTH e).ker := by
    change Theory.PSL2.fieldProjection F (MulAut.congr e (f ⟨t,hQN ht⟩)) = 1
    rw [←MonoidHom.mem_ker,Theory.PSL2.fieldProjection_ker]
    change MulAut.congr e (f ⟨t,hQN ht⟩) ∈ MulAut.innerSubgroup (Theory.PSL2.Group F)
    rw [←MulAut.map_innerSubgroup_congr e]
    exact mem_map_of_mem (MulAut.congr e).toMonoidHom hti
  rw [d.residual_sylow_field_kernel h hTH hS e] at hk
  exact hk

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
variable {G : Type*} [Group G] [Finite G]

/-- In the compatible G₂ row, the left Cartan supplies the entire right
quotient Borel action. It normalizes the intrinsic LT-core, so the binary
Borel actor theorem puts this core in the original S. -/
theorem Preparation.g2_left_core_le_sourceS
    {κ : GroupClass} {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H)) (h : Input κ T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    (he : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.G2.amalgam (F := F))) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.G2.amalgam (F := F)).reverse)) :
    (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤ sourceS L H := by
  have hs := d.g2_local_structure h hTH hp F he
  have hS := hs.2.2.2.2
  have hq : 2 < Nat.card F := by
    rw [hs.1]
    exact Nat.pow_lt_pow_right (by decide : 1 < (2:ℕ)) h.exponent
  rcases he with he | he
  · exact (d.not_g2_short_left_parabolic h hTH hp (he.map fun e => e.left)).elim
  obtain ⟨e⟩ := he
  let P := ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0
  let R := ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1
  let K := residual H
  let fL : P →* Model F := (parabolic₂ (F := F)).subtype.comp e.left.toMonoidHom
  let fR : R →* Model F := (parabolic₁ (F := F)).subtype.comp e.right.toMonoidHom
  have hfL : Function.Injective fL := (parabolic₂ (F := F)).subtype_injective.comp e.left.injective
  have hfR : Function.Injective fR := (parabolic₁ (F := F)).subtype_injective.comp e.right.injective
  have hLP : L ≤ P := le_sup_left.trans le_sup_left
  have hKR : K ≤ R := le_sup_left.trans le_sup_left
  have hLf : (L.subgroupOf P).map fL = local₂ := by
    have hL : L.subgroupOf P = solvableResidual P := by
      apply map_injective P.subtype_injective
      rw [map_subgroupOf_eq_of_le hLP]
      exact (d.parabolic_residuals h hTH hp 0).symm
    rw [hL,show fL = (parabolic₂ (F := F)).subtype.comp e.left.toMonoidHom from rfl,
      ←map_map,map_solvableResidual_eq e.left.toMonoidHom e.left.surjective]
    exact HigherFieldResiduals.parabolic₂_residual hq
  have hKf : (K.subgroupOf R).map fR = local₁ := by
    have hK : K.subgroupOf R = solvableResidual R := by
      apply map_injective R.subtype_injective
      rw [map_subgroupOf_eq_of_le hKR]
      exact (d.parabolic_residuals h hTH hp 1).symm
    rw [hK,show fR = (parabolic₁ (F := F)).subtype.comp e.right.toMonoidHom from rfl,
      ←map_map,map_solvableResidual_eq e.right.toMonoidHom e.right.surjective]
    exact HigherFieldResiduals.parabolic₁_residual hq
  let eK : K ≃* local₁ (F := F) :=
    ((subgroupOfEquivOfLe hKR).symm.trans
      ((K.subgroupOf R).equivMapOfInjective fR hfR)).trans (MulEquiv.subgroupCongr hKf)
  let eQ := (QuotientGroup.congr _ _ eK (pCore_map_iso 2 eK)).trans local₁CoreQuotientEquivPSL
  have heK (k : K) : (eK k).val = fR ⟨k,hKR k.property⟩ := rfl
  have heQ (k : K) : eQ (QuotientGroup.mk' (pCore 2 K) k) =
      QuotientGroup.mk' (center SL(2,F)) (shortSLHom (eK k)) := rfl
  apply d.left_core_le_sourceS_of_borel_action h hTH hS eQ
  intro k hk
  have hSK : sourceS L H ≤ K := hS 1
  have hSL : sourceS L H ≤ L := hS 0
  have hSTK : sourceS L H = (T : Subgroup G) ⊓ K :=
    (d.ordinary_sylow_core_geometry h hTH hS).1 1
  have hSTL : sourceS L H = (T : Subgroup G) ⊓ L :=
    (d.ordinary_sylow_core_geometry h hTH hS).1 0
  have hkB : k.val ∈ ChapterF.Source.borel K (sourceS L H) := by
    change k.val ∈ K ⊓ normalizer ((sourceS L H ⊓ K : Subgroup G) : Set G)
    rw [inf_eq_left.mpr hSK,hSTK]
    exact hk
  have hkP : k.val ∈ P := mem_sup_right hkB
  let b : (P ⊓ R : Subgroup G) := ⟨k.val,hkP,hKR k.property⟩
  have hgB : (eK k).val ∈ Atlas.G2.borel := by
    have hh := congrArg Subtype.val (e.right_commutes b)
    change fR ⟨k.val,hKR k.property⟩ = (e.middle b).val at hh
    rw [heK,hh]
    exact (ChapterF.GreenBook.LieModels.G2.overlap_eq_borel (F := F)).le (e.middle b).property
  obtain ⟨y,hyL,hyB,hyaction⟩ := G2CoreComparison.left_borel_action_lift (eK k) hgB
  let a : R := e.right.symm ⟨y,borel_le_parabolic₁ hyB⟩
  let aL : P := e.left.symm ⟨y,borel_le_parabolic₂ hyB⟩
  let ym : ChapterF.GreenBook.LieModels.G2.overlap (F := F) :=
    ⟨y,borel_le_parabolic₁ hyB,borel_le_parabolic₂ hyB⟩
  have haLR : aL.val = a.val :=
    (congrArg Subtype.val (e.symm.left_commutes ym)).trans
      (congrArg Subtype.val (e.symm.right_commutes ym)).symm
  have haLf : fL aL = y := congrArg Subtype.val (e.left.apply_symm_apply _)
  have haRf : fR a = y := congrArg Subtype.val (e.right.apply_symm_apply _)
  have haL : a.val ∈ L := by
    rw [←haLR]
    have hh : fL aL ∈ (L.subgroupOf P).map fL := hLf.symm ▸ (haLf.symm ▸ hyL)
    exact (mem_map_iff_mem hfL).mp hh
  have hac : a.val ∈ ChapterF.Source.commonBorel ![L,K] (sourceS L H) := by
    rw [←ChapterF.Source.lemma_F_1_3_6 (d.hypothesisF11 h hTH)]
    exact ⟨haLR ▸ aL.property,a.property⟩
  have haS : a.val ∈ normalizer (sourceS L H : Set G) := by
    have hh := (d.hypothesisF11 h hTH).commonBorel_normalizes_localSylow 0 hac
    change a.val ∈ normalizer ((sourceS L H ⊓ L : Subgroup G) : Set G) at hh
    simpa only [inf_eq_left.mpr hSL] using hh
  have haB : a.val ∈ localBorel T L := by
    refine ⟨haL,?_⟩
    rwa [←hSTL]
  have hRN : R ≤ normalizer (K : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hKR).mp
      ((d.hypothesisF11 h hTH).local_normal_in_parabolic 1)
  refine ⟨⟨a.val,hRN a.property⟩,haB,?_⟩
  ext z
  obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 K) z
  rw [pCoreNormalizerAction_mk]
  change QuotientGroup.mk' (pCore 2 K) (K.normalizerMonoidHom ⟨a.val,hRN a.property⟩ x) =
    QuotientGroup.mk' (pCore 2 K) k * QuotientGroup.mk' (pCore 2 K) x * (QuotientGroup.mk' (pCore 2 K) k)⁻¹
  rw [←map_inv,←map_mul,←map_mul]
  apply eQ.injective
  rw [heQ,heQ]
  apply congrArg (QuotientGroup.mk' (center SL(2,F)))
  have haact : eK (K.normalizerMonoidHom ⟨a.val,hRN a.property⟩ x) =
      local₁.normalizerMonoidHom ⟨y,borel_normalizes_local₁ hyB⟩ (eK x) := by
    apply Subtype.ext
    rw [heK]
    change fR ⟨a.val*x.val*a.val⁻¹,_⟩ = y*(eK x).val*y⁻¹
    have hh : (⟨a.val*x.val*a.val⁻¹,_⟩ : R) = a*⟨x.val,hKR x.property⟩*a⁻¹ := Subtype.ext rfl
    rw [hh,map_mul,map_mul,map_inv,haRf,←heK]
  rw [haact,hyaction]
  simp only [map_mul,map_inv]

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
variable {G : Type*} [Group G] [Finite G]

/-- The original G₂ center fixer belongs to S at every original degree. -/
theorem Preparation.g2_center_fixer_le_sourceS
    {κ : GroupClass} {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H)) (h : Input κ T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    (he : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.G2.amalgam (F := F))) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.G2.amalgam (F := F)).reverse)) :
    (T : Subgroup G) ⊓ centralizer
      (((center (residual H)).map (residual H).subtype : Subgroup G) : Set G) ≤ sourceS L H := by
  exact (d.g2_center_fixer_le_left_core_join_sourceS h hTH hp F he).trans
    (sup_le (d.g2_left_core_le_sourceS h hTH hp F he) le_rfl)

/-- Marked G₂ short-root nonfusion with the original center-fixer premise
now discharged, including even field exponents. -/
theorem Preparation.g2_short_root_not_fused
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    (he : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.G2.amalgam (F := F))) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.G2.amalgam (F := F)).reverse)) :
    let Q := (residual H).pCoreIn 2
    let Z := (center (residual H)).map (residual H).subtype
    ∃ e : RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.G2.amalgam (F := F)).reverse,
      ∃ v ∈ Q, (∃ w : ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1,
        w.val=v ∧ (e.right w).val=Atlas.G2.rootC (1:F)) ∧
      v ∉ Z ∧ orderOf v=2 ∧ ∀ g : G, v ∉ Z.conjBy g := by
  exact d.g2_short_root_not_fused_of_centralizer_le h hH hp F he
    (d.g2_center_fixer_le_sourceS h hH.1.1.2 hp F he)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
