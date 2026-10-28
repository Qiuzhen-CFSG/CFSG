module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.IntrinsicCenterIntersection
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.CenterOmegaImage
public import Theory.Representation.BinaryConjugationSection.FixedQuotientIndex
public import Theory.GroupTheory.PCoreInRestriction

/-!
# The intrinsic critical-center image and the remaining exceptional beta indices

The critical-center image is elementary, normal in the actual edge Sylow,
nontrivial, and contained in its omega-center. In the exceptional quotient
of order 144, the normal elementary nine-group embeds a Sylow complement
in GL₂(3). Its semidihedral center has order two, forcing the image to be
the entire omega-center. The genuine rank-one rows use the earlier fusion
argument. Thus the image equality needs neither local catalogue.

In the exceptional row the seed index is exactly two and the full edge
Sylow quotient has order sixteen. Multiplicativity gives index eight over
Z_alpha Q_beta and bounds the index over Q_alpha Q_beta by eight. Transport
retains the original subgroup inclusion and the full original Borel core.
Consequently a seed index different from two discharges the beta catalogue.
NonElementarySeedCatalogue applies this criterion to the actual source
orders, central layers, natural quotient and universal-tree path inputs.

The image-order-two exceptional case is not excluded here. The remaining
nonelementary alpha catalogue and Chapter 14 marked assembly stay open.
Source: DGS, Groups and Graphs (1985), (11.2)(b), p.168, and the index
comparison in (11.4), pp.171--172. The strict enlargement is an extra
F.1.9 reduction alternative, not a row of the printed DGS catalogue.
The semidihedral presentation is ABG II.2, Lemma 1, as proved in
Theory.SpecificGroups.GL2.SemidihedralSylow.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory Representation.BinaryConjugationSection
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Subgroup.CosetGeometry.RankTwo CommutingNontrivial Theory.GroupTheory.AmalgamGraph
open Reduction Representation.AffineNine

private theorem center_card_of_sixteen_embedding
    {H : Type*} [Group H] [Finite H] (hH : Nat.card H = 16)
    (f : H →* GL (Fin 2) (ZMod 3)) (hf : Function.Injective f) :
    Nat.card (center H) = 2 := by
  let U := f.range
  have hU : Nat.card U = 16 := (Nat.card_congr (MonoidHom.ofInjective hf).symm.toEquiv).trans hH
  have hp : IsPGroup 2 U := IsPGroup.of_card (p := 2) (n := 4) hU
  have hGL : Nat.card (GL (Fin 2) (ZMod 3)) = 48 := by
    rw [Matrix.card_GL_field]
    norm_num [Fin.prod_univ_succ,ZMod.card]
  have hi : U.index = 3 := by
    have hc := U.card_mul_index
    rw [hU,hGL] at hc
    omega
  let T := hp.toSylow (by rw [hi]; decide)
  obtain ⟨S,n,hn,hS,a,b,ha,hb,hc,hg,hcenter,_⟩ :=
    Matrix.GeneralLinearGroup.exists_semidihedral_sylow (ZMod 3) (by norm_num [Nat.card_zmod])
  have hSc : Nat.card S = 16 := by
    rw [S.card_eq_multiplicity,hGL]
    decide +kernel
  have hn4 : n = 4 := (Nat.pow_right_injective (by decide : 1 < 2)) (hS.symm.trans hSc)
  subst n
  norm_num only at ha hcenter
  let e : H ≃* S := (MonoidHom.ofInjective hf).trans (T.equiv S)
  rw [Nat.card_congr (centerCongr e).toEquiv,hcenter,Nat.card_zpowers,
    orderOf_pow' a (by decide : (4:ℕ) ≠ 0),ha]
  decide

private theorem omega_card_le_two_of_normal_nine
    {D : Type*} [Group D] [Finite D] (hD : Nat.card D = 144)
    (N : Subgroup D) [N.Normal] [IsElementaryAbelian 3 N]
    (hN : Nat.card N = 9) (hcore : pCore 2 D = ⊥)
    (S : Sylow 2 D) : Nat.card (omegaCenterIn (S : Subgroup D)) ≤ 2 := by
  have hS : Nat.card S = 16 := by
    rw [S.card_eq_multiplicity,hD]
    decide +kernel
  have hNS : N.IsComplement' (S : Subgroup D) := by
    apply isComplement'_of_coprime
    · rw [hN,hS,hD]
    · rw [hN,hS]; decide
  have hc := centralizer_eq_nine_of_twoCore_eq_bot N S S.isPGroup' hNS.sup_eq_top hcore
  let a := (MulAut.conjNormal : D →* MulAut N).comp (S : Subgroup D).subtype
  have ha : Function.Injective a := by
    apply a.ker_eq_bot_iff.mp
    apply (eq_bot_iff_forall _).mpr
    intro s hs
    have hsN : (s : D) ∈ N := by
      rw [←hc,←MulAut.conjNormal_ker_eq_centralizer N]
      exact hs
    exact Subtype.ext (mem_bot.mp (hNS.disjoint.le_bot ⟨hsN,s.property⟩))
  obtain ⟨f,hf⟩ := IsElementaryAbelian.exists_injective_mulAut_generalLinear_of_card_le
    (p := 3) (n := 2) N (by rw [hN]; decide)
  have hcent := center_card_of_sixteen_embedding hS (f.comp a) (hf.comp ha)
  let j : omegaCenterIn (S : Subgroup D) → center S := fun x =>
    ⟨⟨x,((mem_omegaCenterIn_iff _ _).mp x.property).1⟩,mem_center_iff.mpr
      (fun y => Subtype.ext (((mem_omegaCenterIn_iff _ _).mp x.property).2.1 y y.property))⟩
  have hj : Function.Injective j := by
    intro x y he
    exact Subtype.ext (congrArg (fun z : center S => (z.val : D)) he)
  exact (Nat.card_le_card_of_injective j hj).trans hcent.le

variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F" => family (fun i => Subgroup.subgroupOf (P₀ L S i) (Reduction.G₀ L S))
local notation "G₀" => Reduction.G₀ L S

/-- The critical-center image is the actual Sylow omega-center, including
the exceptional order-144 quotient. Neither catalogue is assumed. -/
theorem reduced_intrinsic_center_image_omega (h : HypothesisF11 L S)
    {a b : Vertex F} (hc : IsCriticalPair F a b) (hb : DGS85.b F = 1)
    (T : Sylow 2 (graphLocalGroup F b))
    (hT : (T : Subgroup (graphLocalGroup F b)).map (graphLocalGroup F b).subtype =
      (stabilizer F b ⊓ stabilizer F a).pCoreIn 2) :
    ((Z F a).subgroupOf (graphLocalGroup F b)).map
        (QuotientGroup.mk' (pCore 2 (graphLocalGroup F b))) =
      omegaCenterIn ((T : Subgroup (graphLocalGroup F b)).map
        (QuotientGroup.mk' (pCore 2 (graphLocalGroup F b)))) := by
  let ht := reduced_triple h
  let d := reducedFullEarlierLocalTheorems h
  let := finite_endpoints ht
  let := source_center_elementary ht a
  let M := graphLocalGroup F b
  let : Finite M := Finite.of_injective (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  have hs := reduced_graph_rankOne_or_normal_nine h b
  dsimp only [reducedFamily] at hs
  rcases hs with Mb | ⟨hcard,N,hN,hE,h9⟩
  · exact source_rankOne_center_image_omega ht (reduced_borel_core_sylow h) d hc hb Mb T hT
  · let := hN
    let := hE
    have hab := source_critical_one_adjacent hc hb
    have hZaT : Z F a ≤ (T : Subgroup M).map M.subtype := by
      rw [hT,inf_comm]
      exact ((source_Z_Q_U ht a).1.trans (map_subtype_le _)).trans
        (Noncommuting.graph_Q_le_edgeCore ht hab)
    have hZaM : Z F a ≤ M := hZaT.trans (map_subtype_le _)
    let A := (Z F a).subgroupOf M
    let : IsElementaryAbelian 2 A := IsElementaryAbelian.subgroupOf hZaM
    let q := QuotientGroup.mk' (pCore 2 M)
    let : IsElementaryAbelian 2 (A.map q) := IsElementaryAbelian.map q
    have hAT : A ≤ (T : Subgroup M) := by
      intro x hx
      obtain ⟨y,hy,he⟩ := hZaT hx
      exact (Subtype.ext he : y = x) ▸ hy
    have hn : (T : Subgroup M) ≤ normalizer (A : Set M) := by
      intro x hx
      apply le_normalizer_comap M.subtype
      apply stabilizer_normalizes_Z F a
      exact ((pCoreIn_le 2 _).trans inf_le_right) (hT ▸ mem_map_of_mem M.subtype hx)
    let T' := T.mapSurjective (f := q) (QuotientGroup.mk'_surjective _)
    have hle := reduced_normal_elementary_le_sylow_omega h b T' (A.map q)
      (map_mono hAT) ((map_mono hn).trans (le_normalizer_map q))
    have hu := omega_card_le_two_of_normal_nine hcard N h9 (pCore_quotient_pCore_eq_bot 2) T'
    have hne : A.map q ≠ ⊥ := by
      intro he
      have hk := (Subgroup.map_eq_bot_iff _).mp he
      rw [QuotientGroup.ker_mk'] at hk
      apply hc.2
      have hh := map_mono (f := M.subtype) hk
      rw [map_subgroupOf_eq_of_le hZaM] at hh
      exact (hh.trans_eq (localGroup_core_eq F d b)).trans (source_Z_Q_U ht b).2
    have hp := Nat.card_pos (α := A.map q)
    have hn1 : Nat.card (A.map q) ≠ 1 := fun he => hne (Subgroup.card_eq_one.mp he)
    change Nat.card (omegaCenterIn ((T : Subgroup M).map q)) ≤ 2 at hu
    change A.map q = omegaCenterIn ((T : Subgroup M).map q)
    exact eq_of_le_of_card_ge hle (by omega)

/-- The actual beta critical-center image has order two in the exceptional
normal-nine row. Its full edge Sylow quotient has order sixteen. -/
private theorem exceptional_beta_indices (h : HypothesisF11 L S)
    {a b : Vertex F} (hc : IsCriticalPair F a b) (hb : DGS85.b F = 1)
    (hcard : Nat.card (graphLocalGroup F b ⧸ pCore 2 (graphLocalGroup F b)) = 144)
    (N : Subgroup (graphLocalGroup F b ⧸ pCore 2 (graphLocalGroup F b)))
    [N.Normal] [IsElementaryAbelian 3 N] (h9 : Nat.card N = 9) :
    (Q F b).relIndex (Z F a) = 2 ∧
      (Q F b).relIndex ((stabilizer F a ⊓ stabilizer F b).pCoreIn 2) = 16 := by
  let ht := reduced_triple h
  let d := reducedFullEarlierLocalTheorems h
  let := finite_endpoints ht
  let := source_center_elementary ht a
  let M := graphLocalGroup F b
  let : Finite M := Finite.of_injective (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  have hab := source_critical_one_adjacent hc hb
  obtain ⟨T,hT⟩ := source_edge_core_local_sylow ht (reduced_borel_core_sylow h) d hab.symm
  change Sylow 2 M at T
  change (T : Subgroup M).map M.subtype = (stabilizer F b ⊓ stabilizer F a).pCoreIn 2 at hT
  have hZaT : Z F a ≤ (T : Subgroup M).map M.subtype := by
    rw [hT,inf_comm]
    exact ((source_Z_Q_U ht a).1.trans (map_subtype_le _)).trans
      (Noncommuting.graph_Q_le_edgeCore ht hab)
  have hZaM : Z F a ≤ M := hZaT.trans (map_subtype_le _)
  let q := QuotientGroup.mk' (pCore 2 M)
  let T' := T.mapSurjective (f := q) (QuotientGroup.mk'_surjective _)
  let A := ((Z F a).subgroupOf M).map q
  have hi : Nat.card A = (Q F b).relIndex (Z F a) :=
    actor_image_card_eq_relIndex M (Q F b) (Z F a) q
      (local_quotient_kernel F d b (MulEquiv.refl _)) hZaM
  have he : A = omegaCenterIn (T' : Subgroup (M ⧸ pCore 2 M)) :=
    reduced_intrinsic_center_image_omega h hc hb T hT
  have hu := omega_card_le_two_of_normal_nine hcard N h9 (pCore_quotient_pCore_eq_bot 2) T'
  rw [←he,hi] at hu
  have hp : 0 < (Q F b).relIndex (Z F a) := hi ▸ Nat.card_pos
  have hn : (Q F b).relIndex (Z F a) ≠ 1 := fun he =>
    hc.2 ((relIndex_eq_one.mp he).trans (source_Z_Q_U ht b).2)
  refine ⟨by omega,?_⟩
  rw [inf_comm (stabilizer F a),←hT,←localGroup_core_eq F d b]
  change ((pCore 2 M).map M.subtype).relIndex ((T : Subgroup M).map M.subtype) = _
  rw [relIndex_map_map_of_injective _ _ M.subtype_injective,
    ←show q.ker = pCore 2 M from QuotientGroup.ker_mk' _,relIndex_ker]
  change Nat.card T' = 16
  rw [T'.card_eq_multiplicity,hcard]
  decide +kernel

/-- The only possible missing beta catalogue has a critical-center image
of order two, a Sylow quotient of order sixteen, and index eight over the
critical-center supplement. These are indices in the actual source groups. -/
theorem reduced_beta_model_or_small_seed (h : HypothesisF11 L S)
    {a b : Vertex F} (hc : IsCriticalPair F a b) (hb : DGS85.b F = 1) :
    IsRankOneModel (graphLocalGroup F b ⧸ pCore 2 (graphLocalGroup F b)) ∨
      (Nat.card (graphLocalGroup F b ⧸ pCore 2 (graphLocalGroup F b)) = 144 ∧
        (Q F b).relIndex (Z F a) = 2 ∧
        (Q F b).relIndex ((stabilizer F a ⊓ stabilizer F b).pCoreIn 2) = 16 ∧
        (Z F a ⊔ Q F b).relIndex ((stabilizer F a ⊓ stabilizer F b).pCoreIn 2) = 8 ∧
        (Q F a ⊔ Q F b).relIndex ((stabilizer F a ⊓ stabilizer F b).pCoreIn 2) ≤ 8) := by
  have hs := reduced_graph_rankOne_or_normal_nine h b
  dsimp only [reducedFamily] at hs
  rcases hs with Mb | ⟨hcard,N,hN,hE,h9⟩
  · exact Or.inl Mb
  · let ht := reduced_triple h
    let := finite_endpoints ht
    let := hN
    let := hE
    obtain ⟨hi,he⟩ := exceptional_beta_indices h hc hb hcard N h9
    have hab := source_critical_one_adjacent hc hb
    let R := (stabilizer F a ⊓ stabilizer F b).pCoreIn 2
    let : Finite R := Finite.of_injective
      (inclusion ((pCoreIn_le 2 _).trans inf_le_left)) (inclusion_injective _)
    have hQa : Q F a ≤ R := Noncommuting.graph_Q_le_edgeCore ht hab
    have hQb : Q F b ≤ R := by
      simpa only [R,inf_comm] using Noncommuting.graph_Q_le_edgeCore ht hab.symm
    have hZa : Z F a ≤ Q F a := (source_Z_Q_U ht a).1.trans (map_subtype_le _)
    let : ((Q F b).subgroupOf R).Normal := normal_subgroupOf_of_le_normalizer
      (((pCoreIn_le 2 _).trans inf_le_right).trans (stabilizer_normalizes_Q F b))
    have hi' : (Q F b).relIndex (Z F a ⊔ Q F b) = 2 := by
      have hh := relIndex_sup_left ((Z F a).subgroupOf R) ((Q F b).subgroupOf R)
      rw [←subgroupOf_sup hQb (hZa.trans hQa),
        relIndex_subgroupOf (sup_le hQb (hZa.trans hQa)),
        relIndex_subgroupOf (hZa.trans hQa)] at hh
      rw [sup_comm]
      exact hh.trans hi
    have hm := relIndex_mul_relIndex (Q F b) (Z F a ⊔ Q F b) R le_sup_right
      (sup_le (hZa.trans hQa) hQb)
    rw [hi',he] at hm
    have hs8 : (Z F a ⊔ Q F b).relIndex R = 8 := by omega
    refine Or.inr ⟨hcard,hi,he,hs8,?_⟩
    rw [←hs8]
    exact relIndex_le_of_le_left (sup_le_sup_right hZa _) (by exact index_ne_zero_of_finite)

/-- A critical-center image other than order two discharges the beta
catalogue, without assuming an alpha catalogue or nonsolvability. -/
theorem reduced_beta_model_of_seed_index_ne_two (h : HypothesisF11 L S)
    {a b : Vertex F} (hc : IsCriticalPair F a b) (hb : DGS85.b F = 1)
    (hi : (Q F b).relIndex (Z F a) ≠ 2) :
    IsRankOneModel (graphLocalGroup F b ⧸ pCore 2 (graphLocalGroup F b)) := by
  exact (reduced_beta_model_or_small_seed h hc hb).resolve_right (fun he => hi he.2.1)

/-- The original subgroup inclusion retains the beta exclusion criterion
and constructs a marking of that very quotient. -/
theorem original_reduced_beta_model_of_seed_index_ne_two (h : HypothesisF11 L S)
    {a b : Vertex F} (hc : IsCriticalPair F a b) (hb : DGS85.b F = 1)
    (hi : ((Q F b).map (G₀).subtype).relIndex ((Z F a).map (G₀).subtype) ≠ 2) :
    IsRankOneModel ((graphLocalGroup F b).map (G₀).subtype ⧸
      pCore 2 ((graphLocalGroup F b).map (G₀).subtype)) := by
  rw [relIndex_map_map_of_injective _ _ (G₀).subtype_injective] at hi
  let e := (graphLocalGroup F b).equivMapOfInjective (G₀).subtype (G₀).subtype_injective
  exact (reduced_beta_model_of_seed_index_ne_two h hc hb hi).of_equiv
    (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).symm

/-- The same exhaustive alternative on the full original Borel. The
exceptional indices use its actual two-core and the original center/core
images, without replacing the Borel by a selected Sylow. -/
theorem original_borel_beta_model_or_small_seed (h : HypothesisF11 L S)
    (hc : IsCriticalPair F (base F false) (base F true)) (hb : DGS85.b F = 1) :
    IsRankOneModel ((graphLocalGroup F (base F true)).map (G₀).subtype ⧸
      pCore 2 ((graphLocalGroup F (base F true)).map (G₀).subtype)) ∨
      (Nat.card ((graphLocalGroup F (base F true)).map (G₀).subtype ⧸
          pCore 2 ((graphLocalGroup F (base F true)).map (G₀).subtype)) = 144 ∧
        ((Q F (base F true)).map (G₀).subtype).relIndex
          ((Z F (base F false)).map (G₀).subtype) = 2 ∧
        ((Q F (base F true)).map (G₀).subtype).relIndex (twoCore (commonBorel L S)) = 16 ∧
        ((Z F (base F false)).map (G₀).subtype ⊔
          (Q F (base F true)).map (G₀).subtype).relIndex (twoCore (commonBorel L S)) = 8 ∧
        ((Q F (base F false)).map (G₀).subtype ⊔
          (Q F (base F true)).map (G₀).subtype).relIndex (twoCore (commonBorel L S)) ≤ 8) := by
  let e := (graphLocalGroup F (base F true)).equivMapOfInjective
    (G₀).subtype (G₀).subtype_injective
  let eq := QuotientGroup.congr _ _ e (pCore_map_iso 2 e)
  rcases reduced_beta_model_or_small_seed h hc hb with Mb | ⟨hcard,hseed,hedge,hcenter,hprod⟩
  · exact Or.inl (Mb.of_equiv eq.symm)
  · let R := (stabilizer F (base F false) ⊓ stabilizer F (base F true)).pCoreIn 2
    have htr := reduced_triple h
    have hBG : B₀ L S ≤ G₀ :=
      (show B₀ L S ≤ P₀ L S 0 from le_sup_right).trans le_sup_left
    have hRG : twoCore (commonBorel L S) ≤ G₀ :=
      (show twoCore (commonBorel L S) ≤ B₀ L S from le_sup_right).trans hBG
    have hmap : R.map (G₀).subtype = twoCore (commonBorel L S) := by
      dsimp only [R]
      rw [show stabilizer F (base F false) = F false from Subgroup.CosetGeometry.stabilizer_base _ _,
        show stabilizer F (base F true) = F true from Subgroup.CosetGeometry.stabilizer_base _ _,
        show F false ⊓ F true = (B₀ L S).subgroupOf G₀ from htr.intersection,
        pCoreIn_subgroupOf 2 _ _ hBG,B₀_core h]
      exact map_subgroupOf_eq_of_le hRG
    right
    refine ⟨(Nat.card_congr eq.symm.toEquiv).trans hcard,?_,?_,?_,?_⟩
    · rwa [relIndex_map_map_of_injective _ _ (G₀).subtype_injective]
    · rwa [←hmap,relIndex_map_map_of_injective _ _ (G₀).subtype_injective]
    · rwa [←hmap,←Subgroup.map_sup,relIndex_map_map_of_injective _ _ (G₀).subtype_injective]
    · rwa [←hmap,←Subgroup.map_sup,relIndex_map_map_of_injective _ _ (G₀).subtype_injective]

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
