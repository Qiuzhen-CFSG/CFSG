module
public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceUpperAction
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.fourLetter
public import CFSG.Quasithin.ChapterG.Section02.AlternatingFive.Recognition.ProjectiveGeometry.Standard
public import CFSG.Quasithin.ChapterG.Section02.RankOneHigherFields.QuotientAction.ProjectiveOrbit.Geometry
public import Theory.SpecificGroups.SL2.CardFourEquiv
public import Theory.SpecificGroups.SL2.FieldAutomorphismCore

/-!
# The Borel and root markings of the original A₅ quotient

The literal L₁ image has order twelve and normalizes the U_H image of
order four. Index five and the trivial two-core of A₅ identify that image
with the full root normalizer. Sylow conjugacy supplies an actual SL₂(4)
model carrying the U_H image to the standard root. The original mover
lies outside its Borel, and that Borel preserves the original W image.

Source: Aschbacher–Smith,G.1.5(1,3) and G.2.4(1,6), printed pp.328,334,
applied to13.5.14–15, printed pp.919–920.
-/

@[expose] public section
open Subgroup
open scoped MatrixGroups Pointwise
namespace CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceUpperBorel
open Section08.SourceCompletion
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open PlaneGeometry.TwoBlocks
open SourceFiveModule SourceUpperStructure
open ChapterG.Section02.AlternatingFive.Recognition
open ChapterG.Section02.AlternatingFive.Recognition.ProjectiveGeometry
open ChapterG.Section02.RankOneHigherFields.QuotientAction.Projective
variable {G : Type*} [Group G] [Finite G] {D : ChapterF.Section09.Setup G}
  {V₂ M : Subgroup G}
  (d : NaturalSetup D.T D.L D.V D.V₁ V₂ D.Vplus M D.Gz)

theorem local_image_card (h : D.Hypothesis) (g : D.L)
    (hK : NormalBranch.K D g.val ≤ D.L) (hL : D.L₁ ≤ NormalBranch.K D g.val)
    (a : alternatingGroup (Fin 6))
    (hi : ((NormalBranch.K D g.val).subgroupOf D.L).map (localMap d) =
      FivePair.five.map (MulAut.conj a.val).toMonoidHom) :
    Nat.card ((D.L₁.subgroupOf (NormalBranch.K D g.val)).map (restrictedActor d hK a hi))=12 := by
  let B := D.L₁.subgroupOf (NormalBranch.K D g.val)
  let f := restrictedActor d hK a hi
  let q := (localMap d).comp (inclusion hK)
  have he : f.ker=q.ker := restrictedActor_ker d hK a hi
  rw [←relIndex_ker,he,relIndex_ker]
  have hmap : B.map (inclusion hK)=D.L₁.subgroupOf D.L := by
    apply map_injective D.L.subtype_injective
    rw [map_map]
    change B.map (NormalBranch.K D g.val).subtype = _
    rw [map_subgroupOf_eq_of_le hL,map_subgroupOf_eq_of_le (hL.trans hK)]
  change Nat.card (B.map q)=12
  rw [show B.map q=(D.L₁.subgroupOf D.L).map (localMap d) by
    change B.map ((localMap d).comp (inclusion hK)) = _
    rw [←map_map,hmap]]
  obtain ⟨b,hb,_⟩ := QuadraticSource.source_even_flag d
  rw [SourcePointCore.local_residual_marking d h b hb,
    card_map_of_injective (MulAut.conj b.val).injective,card_K]

theorem local_image_eq_normalizer (h : D.Hypothesis)
    (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6))
    (hseed : D.Vplus = ⁅D.V,D.L₁⁆) (hn : (D.L₁.subgroupOf D.H).Normal)
    (hU : ¬ IsMulCommutative D.UH) (g : D.L)
    (hK : NormalBranch.K D g.val ≤ D.L) (hL : D.L₁ ≤ NormalBranch.K D g.val)
    (a : alternatingGroup (Fin 6))
    (hi : ((NormalBranch.K D g.val).subgroupOf D.L).map (localMap d) =
      FivePair.five.map (MulAut.conj a.val).toMonoidHom) :
    (D.L₁.subgroupOf (NormalBranch.K D g.val)).map (restrictedActor d hK a hi)=
      normalizer (((D.UH.subgroupOf (NormalBranch.K D g.val)).map
        (restrictedActor d hK a hi)) : Set (alternatingGroup (Fin 5))) := by
  let J := NormalBranch.K D g.val
  let U := D.UH.subgroupOf J
  let f := restrictedActor d hK a hi
  let B := (D.L₁.subgroupOf J).map f
  let N := normalizer (U.map f : Set (alternatingGroup (Fin 5)))
  have hBN : B≤N := by
    have hLU : D.L₁≤normalizer (D.UH:Set G) :=
      (le_sup_left.trans h.local_le).trans (le_normalizer_conjugateSpanBy D.Vplus D.H)
    have hl : D.L₁.subgroupOf J≤normalizer (U:Set J) := by
      intro l hl
      apply mem_normalizer_iff.mpr
      intro u
      exact mem_normalizer_iff.mp (hLU hl) u.val
    exact (map_mono hl).trans (U.le_normalizer_map f)
  have hBcard : Nat.card B=12 := local_image_card d h g hK hL a hi
  have hUcard : Nat.card (U.map f)=4 :=
    SourceCoreProduct.closure_image_card d h e hseed hn hU g hK a hi
  have hBindex : B.index=5 := by
    have hh := B.card_mul_index
    rw [hBcard,nat_card_alternatingGroup,Nat.card_fin] at hh
    norm_num [Nat.factorial] at hh
    omega
  have hNne : N≠⊤ := by
    intro he
    let : (U.map f).Normal := normalizer_eq_top_iff.mp he
    have hUp : IsPGroup 2 (U.map f) :=
      ((show IsPGroup 2 D.UH from h.g2_hypothesis.U_isPGroup).comap_subtype).map f
    have hcore : U.map f≤pCore 2 (alternatingGroup (Fin 5)) := le_sSup ⟨inferInstance,hUp⟩
    rw [FivePair.alternating_five_twoCore] at hcore
    have hz := le_bot_iff.mp hcore
    rw [hz,card_bot] at hUcard
    contradiction
  rcases eq_or_lt_of_le hBN with he|hlt
  · exact he
  · have hd := index_dvd_of_le hlt.le
    rw [hBindex] at hd
    rcases (Nat.dvd_prime (by decide : Nat.Prime 5)).mp hd with he|he
    · exact (hNne (index_eq_one.mp he)).elim
    · have hh := index_strictAnti hlt
      rw [he,hBindex] at hh
      omega

theorem upper_marked_model (h : D.Hypothesis)
    (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6))
    (hseed : D.Vplus = ⁅D.V,D.L₁⁆) (hn : (D.L₁.subgroupOf D.H).Normal)
    (hU : ¬ IsMulCommutative D.UH) (g : D.L)
    (hK : NormalBranch.K D g.val ≤ D.L) (a : alternatingGroup (Fin 6))
    (hi : ((NormalBranch.K D g.val).subgroupOf D.L).map (localMap d) =
      FivePair.five.map (MulAut.conj a.val).toMonoidHom) :
    ∃ m : alternatingGroup (Fin 5) ≃* SL(2,F4),
      (((D.UH.subgroupOf (NormalBranch.K D g.val)).map (restrictedActor d hK a hi)).map
        m.toMonoidHom) = RootGroup F4 standardPoint.val := by
  let U := (D.UH.subgroupOf (NormalBranch.K D g.val)).map (restrictedActor d hK a hi)
  have hUp : IsPGroup 2 U :=
    ((show IsPGroup 2 D.UH from h.g2_hypothesis.U_isPGroup).comap_subtype).map _
  have hc : Nat.card U=4 := SourceCoreProduct.closure_image_card d h e hseed hn hU g hK a hi
  have hidx : U.index=15 := by
    have hh := U.card_mul_index
    rw [hc,nat_card_alternatingGroup,Nat.card_fin] at hh
    norm_num [Nat.factorial] at hh
    omega
  let P : Sylow 2 (alternatingGroup (Fin 5)) := hUp.toSylow (by rw [hidx];decide)
  obtain ⟨eA⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four field_card
  let e₀ : alternatingGroup (Fin 5)≃*SL(2,F4) :=
    eA.symm.trans (Atlas.RankOneFieldAutomorphisms.slEquivPSL (F:=F4)).symm
  let R : Sylow 2 SL(2,F4) := P.mapSurjective (f:=e₀.toMonoidHom) e₀.surjective
  obtain ⟨b,hb⟩ := MulAction.exists_smul_eq SL(2,F4) R
    (Matrix.SpecialLinearGroup.upperUnipotentSylow F4 2)
  refine ⟨e₀.trans (MulAut.conj b),?_⟩
  rw [root_standardPoint]
  have hh := congrArg (fun Q:Sylow 2 SL(2,F4)=>(Q:Subgroup SL(2,F4))) hb
  change (U.map e₀.toMonoidHom).map (MulAut.conj b).toMonoidHom =
    Matrix.SpecialLinearGroup.upperUnipotent F4 at hh
  rw [map_map] at hh
  exact hh

theorem mover_not_borel (h : D.Hypothesis)
    (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6))
    (hseed : D.Vplus = ⁅D.V,D.L₁⁆) (hn : (D.L₁.subgroupOf D.H).Normal)
    (hU : ¬ IsMulCommutative D.UH) (g : D.L) (hgn : g.val∉D.Gz)
    (hg : g.val∈NormalBranch.K D g.val)
    (hK : NormalBranch.K D g.val ≤ D.L) (hL : D.L₁ ≤ NormalBranch.K D g.val)
    (a : alternatingGroup (Fin 6))
    (hi : ((NormalBranch.K D g.val).subgroupOf D.L).map (localMap d) =
      FivePair.five.map (MulAut.conj a.val).toMonoidHom) :
    restrictedActor d hK a hi ⟨g.val,hg⟩ ∉ normalizer
      (((D.UH.subgroupOf (NormalBranch.K D g.val)).map (restrictedActor d hK a hi)) :
        Set (alternatingGroup (Fin 5))) := by
  intro hh
  rw [←local_image_eq_normalizer d h e hseed hn hU g hK hL a hi] at hh
  obtain ⟨l,hl,he⟩ := hh
  let k : NormalBranch.K D g.val := ⟨g.val,hg⟩
  have hdiff : l⁻¹*k∈(restrictedActor d hK a hi).ker := by
    change restrictedActor d hK a hi (l⁻¹*k)=1
    rw [map_mul,map_inv,he,inv_mul_cancel]
  rw [restrictedActor_ker_eq_twoCore d hK a hi e] at hdiff
  have hs : l.val⁻¹*g.val∈D.Gz :=
    ((core_centralizes_module d h e g hK a hi).trans
      (centralizer_le (h.point_lt.le.trans h.plus_le)))
        (mem_map_of_mem (NormalBranch.K D g.val).subtype hdiff)
  have hlG : l.val∈D.Gz := ((map_subtype_le _).trans inf_le_right) hl
  apply hgn
  simpa only [mul_inv_cancel_left] using D.Gz.mul_mem hlG hs

theorem upper_borel_invariant (h : D.Hypothesis)
    (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6))
    (hseed : D.Vplus = ⁅D.V,D.L₁⁆) (hn : (D.L₁.subgroupOf D.H).Normal)
    (hU : ¬ IsMulCommutative D.UH) (g : D.L)
    (hK : NormalBranch.K D g.val ≤ D.L) (hL : D.L₁ ≤ NormalBranch.K D g.val)
    (a : alternatingGroup (Fin 6))
    (hi : ((NormalBranch.K D g.val).subgroupOf D.L).map (localMap d) =
      FivePair.five.map (MulAut.conj a.val).toMonoidHom)
    {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    (σ : Representation (ZMod 2) (alternatingGroup (Fin 5)) E)
    (c : Representation.BinaryConjugationSection (NormalBranch.K D g.val)
      ((NormalBranch.K D g.val).pCoreIn 2) D.V (σ.comp (restrictedActor d hK a hi)))
    (x : alternatingGroup (Fin 5))
    (hx : x∈normalizer (((D.UH.subgroupOf (NormalBranch.K D g.val)).map
      (restrictedActor d hK a hi)) : Set (alternatingGroup (Fin 5)))) :
    (c.imageSpace (D.UH⊓(NormalBranch.K D g.val).pCoreIn 2)).map (σ x)=
      c.imageSpace (D.UH⊓(NormalBranch.K D g.val).pCoreIn 2) := by
  rw [←local_image_eq_normalizer d h e hseed hn hU g hK hL a hi] at hx
  obtain ⟨l,hl,rfl⟩ := hx
  let W := D.UH⊓(NormalBranch.K D g.val).pCoreIn 2
  have hnW : D.L₁≤normalizer (W:Set G) :=
    (le_inf ((le_sup_left.trans h.local_le).trans (le_normalizer_conjugateSpanBy D.Vplus D.H))
      (hL.trans (pair_normalizes_core g))).trans inf_normalizer_le_normalizer_inf
  have he : W.conjBy l.val=W := mem_normalizer_iff_map_conj_eq.mp (hnW hl)
  have hm := c.imageSpace_conjBy W inf_le_right l
  rw [he] at hm
  exact hm.symm

end CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceUpperBorel
end
