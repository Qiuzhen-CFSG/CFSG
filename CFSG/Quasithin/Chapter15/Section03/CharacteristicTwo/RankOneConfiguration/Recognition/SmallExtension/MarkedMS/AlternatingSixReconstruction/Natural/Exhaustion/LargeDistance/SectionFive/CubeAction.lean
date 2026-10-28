module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubeRadical
public import Theory.GroupTheory.CoprimeCentralizerCard
public import Theory.GroupTheory.CentralizerInjectiveImage

/-!
# Cubic movement on the actual three-pair radical

The cubic constructed in `CubeRadical` acts on both the original MS2(a)
radical and the minimum characteristic replacement. On their six-letter
images its commutator is exactly the even plane and its fixed subgroup
maps onto the diagonal involution. Coprime decomposition lifts the fixed
line, while literal pullback identifies the commutator supplements by the
two-cores. The replacement Thompson commutator has that same even image
in both alternatives for the Thompson subgroup.

The pair rotation has no fixed vector on the natural four-space: a
fixed quotient vector lifts to a word whose displacement is constant,
and the two three-cycles and augmentation equation force that word to be
constant. Consequently its fixed subgroup on the actual moved cover is
exactly the ambient central attachment. Coprime decomposition and the
literal natural projection give a commutator of order sixteen for both
the order-sixteen and order-thirty-two covers.

The final original-witness application uses one and the same cubic and
both original projection maps. The Thompson image cannot lie in any
point core: its even plane has no common fixed letter, whereas every even
point core fixes two letters. This supplies an algebraic obstruction for
the shifted-path containment in (5.10); that original-graph argument, the
original Sylow branches and the distance-four estimates remain open.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), Section 5, especially (5.4)--(5.10), printed pp.915--923, and the
characteristic reduction in Section 7, pp.932--933; Aschbacher--Smith
C.1.31 (MS2)(a), printed p.135.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterB.Offenders CFSG.Quasithin.ChapterB.Offenders.Six
open Theory.SpecificGroups.SymmetricSix
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
namespace CubeAction
local notation "S" => Equiv.Perm (Fin 6)
private abbrev r : S := BinaryFlags.pairRotation
private abbrev z : S := dWords 7

private theorem even_moved : ⁅evenPart 6,zpowers r⁆ = evenPart 6 := by
  apply le_antisymm
  · exact (commutator_mono inf_le_left le_rfl).trans
      (by simpa only [commutator_comm,BinaryFlags.D0,evenPart,SixCorePlane.cube_eq] using
        BinaryFlags.rotation_commutator_le_D0)
  · intro x hx
    obtain ⟨i,hi⟩ := (mem_evenPart_iff x).mp hx
    have cert : ∀ i : Fin 4, ∃ j : Fin 4, ⁅planeWords 4 j,r⁆ = planeWords 4 i := by
      decide +kernel
    obtain ⟨j,hj⟩ := cert i
    rw [←hi,←hj]
    exact commutator_mem_commutator ((mem_evenPart_iff _).mpr ⟨j,rfl⟩) (mem_zpowers r)

private theorem cube_moved : ⁅D 6,zpowers r⁆ = evenPart 6 := by
  apply le_antisymm
  · simpa only [commutator_comm,BinaryFlags.D0,evenPart,SixCorePlane.cube_eq] using
      BinaryFlags.rotation_commutator_le_D0
  · rw [←even_moved]
    exact commutator_mono inf_le_left le_rfl

private theorem fixed_cube : D 6 ⊓ centralizer ({r} : Set S) = zpowers z := by
  apply le_antisymm
  · intro x hx
    obtain ⟨i,hi⟩ := (mem_disjointTranspositions_iff (3 : Fin 4) x).mp hx.1
    have hc := mem_centralizer_singleton_iff.mp hx.2
    rw [←hi] at hc ⊢
    have cert : ∀ i : Fin 8, dWords i*r=r*dWords i → i=0 ∨ i=7 := by decide +kernel
    rcases cert i hc with rfl | rfl
    · exact one_mem _
    · exact mem_zpowers z
  · apply zpowers_le.mpr
    exact ⟨(mem_disjointTranspositions_iff (3 : Fin 4) _).mpr ⟨7,rfl⟩,
      mem_centralizer_singleton_iff.mpr (by decide +kernel)⟩

private theorem fixed_cube_order : Nat.card (zpowers z) = 2 := by
  rw [Nat.card_zpowers]
  exact orderOf_eq_prime (by decide +kernel) (by decide +kernel)

private theorem even_ne_cube : evenPart 6 ≠ D 6 := by
  intro he
  have hm : pairSwap 6 0 ∈ evenPart 6 := he.symm ▸ pairSwap_mem (n := 6) (m := 3) 0 (by decide)
  have hh := hm.2
  exact (by decide +kernel : pairSwap 6 0 ∉ alternatingGroup (Fin 6)) hh

private theorem cubic_decomposition {A : Type*} [Group A] [Finite A]
    (T : Subgroup A) (hT : IsPGroup 2 T) (x : A) (ho : orderOf x=3)
    (hx : x ∈ normalizer (T : Set A)) :
    T = ⁅T,zpowers x⁆ ⊔ (T ⊓ centralizer ({x} : Set A)) := by
  have hc : Nat.Coprime (Nat.card (zpowers x)) (Nat.card T) := by
    obtain ⟨n,hn⟩ := hT.exists_card_eq
    rw [Nat.card_zpowers,ho,hn]
    exact Nat.Coprime.pow_right n (by decide)
  simpa only [zpowers_eq_closure,centralizer_closure] using
    eq_commutator_sup_centralizer_of_solvable_coprime T (zpowers x)
      (zpowers_le.mpr hx) (@IsNilpotent.to_isSolvable T _ hT.isNilpotent) hc

private theorem fixed_conjugate (u : S) :
    (D 6).map (MulAut.conj u).toMonoidHom ⊓
      centralizer ({(MulAut.conj u) r} : Set S) =
        (zpowers z).map (MulAut.conj u).toMonoidHom := by
  have he := map_inf_centralizer_of_injective (MulAut.conj u).toMonoidHom
    (MulAut.conj u).injective (D 6) (zpowers r)
  rw [MonoidHom.map_zpowers] at he
  simp only [zpowers_eq_closure,centralizer_closure] at he
  exact he.trans (congrArg (Subgroup.map (MulAut.conj u).toMonoidHom) fixed_cube)

private theorem moved_image {A : Type*} [Group A]
    (q : A →* S) (T : Subgroup A) (x : A) (u : S)
    (hx : q x=(MulAut.conj u) r)
    (hT : T.map q=(evenPart 6).map (MulAut.conj u).toMonoidHom ∨
      T.map q=(D 6).map (MulAut.conj u).toMonoidHom) :
    (⁅T,zpowers x⁆ : Subgroup A).map q =
      (evenPart 6).map (MulAut.conj u).toMonoidHom := by
  have hz : zpowers (q x) = (zpowers r).map (MulAut.conj u).toMonoidHom := by
    rw [MonoidHom.map_zpowers,hx]
    rfl
  rw [map_commutator,MonoidHom.map_zpowers,hz]
  rcases hT with hT | hT
  · rw [hT,←map_commutator,even_moved]
  · rw [hT,←map_commutator,cube_moved]

private theorem cubic_fixed_image {A : Type*} [Group A] [Finite A]
    (q : A →* S) (T : Subgroup A) (hT : IsPGroup 2 T)
    (x : A) (ho : orderOf x=3) (hn : x ∈ normalizer (T : Set A)) (u : S)
    (hx : q x=(MulAut.conj u) r)
    (himage : T.map q=(D 6).map (MulAut.conj u).toMonoidHom) :
    (T ⊓ centralizer ({x} : Set A)).map q =
      (zpowers z).map (MulAut.conj u).toMonoidHom := by
  let C := T ⊓ centralizer ({x} : Set A)
  have hbound : C.map q ≤ (zpowers z).map (MulAut.conj u).toMonoidHom := by
    rw [←fixed_conjugate]
    refine le_inf ((map_mono inf_le_left).trans_eq himage) ?_
    rintro _ ⟨a,ha,rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    have hh := congrArg q (mem_centralizer_singleton_iff.mp ha.2)
    simpa only [map_mul,hx] using hh
  have hnC : C.map q ≠ ⊥ := by
    intro hC
    have he := congrArg (Subgroup.map q) (cubic_decomposition T hT x ho hn)
    rw [Subgroup.map_sup,moved_image q T x u hx (Or.inr himage),hC,sup_bot_eq,himage] at he
    exact even_ne_cube ((map_injective (MulAut.conj u).injective) he.symm)
  apply eq_of_le_of_card_ge hbound
  rw [card_map_of_injective (MulAut.conj u).injective,fixed_cube_order]
  have hpos := Nat.card_pos (α := C.map q)
  have hne : Nat.card (C.map q) ≠ 1 := fun hc => hnC (card_eq_one.mp hc)
  omega

private theorem even_pullback {A : Type*} [Group A]
    (q : A →* S) (T : Subgroup A) (hk : q.ker ≤ T) (u : S)
    (himage : T.map q=(D 6).map (MulAut.conj u).toMonoidHom)
    (W : Subgroup A)
    (hW : W.map q=(evenPart 6).map (MulAut.conj u).toMonoidHom) :
    q.ker ⊔ W = T ⊓ (alternatingGroup (Fin 6)).comap q := by
  have he : (evenPart 6).map (MulAut.conj u).toMonoidHom =
      T.map q ⊓ alternatingGroup (Fin 6) := by
    change (D 6 ⊓ alternatingGroup (Fin 6)).map (MulAut.conj u).toMonoidHom = _
    rw [Subgroup.map_inf _ _ _ (MulAut.conj u).injective,←himage]
    have hA : (alternatingGroup (Fin 6)).map (MulAut.conj u).toMonoidHom =
        alternatingGroup (Fin 6) := mem_normalizer_iff_map_conj_eq.mp
      (show u ∈ normalizer (alternatingGroup (Fin 6) : Set S) by
        rw [normalizer_eq_top]; trivial)
    rw [hA]
  have hh := congrArg (Subgroup.comap q) (hW.trans he)
  rw [comap_inf,comap_map_eq,comap_map_eq,sup_eq_left.mpr hk] at hh
  exact (sup_comm _ _).trans hh

open BinaryPermutation

private theorem natural_fixed_zero (v : BinaryPermutation.natural (Fin 6))
    (hv : BinaryPermutation.naturalRepresentation (Fin 6) r v=v) : v=0 := by
  obtain ⟨w,rfl⟩ := coreToNatural_surjective v
  have hdiff : coreToNatural (Fin 6) (coreRepresentation (Fin 6) r w-w)=0 := by
    rw [map_sub,coreToNatural_equivariant,hv,sub_self]
  have hk : (coreRepresentation (Fin 6) r w-w).val ∈ constants (Fin 6) := by
    apply (Submodule.Quotient.mk_eq_zero _).mp
    exact congrArg Subtype.val hdiff
  obtain ⟨a,ha⟩ := (mem_constants_iff _).mp hk
  have cert : ∀ (v : Fin 6 → ZMod 2) (a : ZMod 2),
      (∑ i,v i)=0 → (∀ i,v (r.symm i)-v i=a) → ∀ i,v i=v 0 := by decide +kernel
  have hc : w.val ∈ constants (Fin 6) :=
    (mem_constants_iff _).mpr ⟨w.val 0,cert w.val a w.property ha⟩
  apply Subtype.ext
  exact (Submodule.Quotient.mk_eq_zero _).mpr hc

private theorem natural_conjugate_fixed_zero (u : S)
    (v : BinaryPermutation.natural (Fin 6))
    (hv : BinaryPermutation.naturalRepresentation (Fin 6) ((MulAut.conj u) r) v=v) : v=0 := by
  let ρ := BinaryPermutation.naturalRepresentation (Fin 6)
  change ρ ((MulAut.conj u) r) v=v at hv
  have he : ρ r (ρ u⁻¹ v)=ρ u⁻¹ v := by
    have hh := congrArg (fun w => ρ u⁻¹ w) hv
    simpa only [←Module.End.mul_apply,←map_mul,MulAut.conj_apply,inv_mul_cancel_left,
      mul_assoc] using hh
  have hz := natural_fixed_zero (ρ u⁻¹ v) he
  have hh := congrArg (fun w => ρ u w) hz
  simpa only [←Module.End.mul_apply,←map_mul,mul_inv_cancel,map_one,
    Module.End.one_apply,map_zero] using hh

private theorem even_not_point (u v : S) :
    ¬ (evenPart 6).map (MulAut.conj u).toMonoidHom ≤
      BinaryFlags.pointCore.map (MulAut.conj v).toMonoidHom := by
  intro hle
  have hfix (a : S) (ha : a ∈ evenPart 6) :
      a (u.symm (v 4))=u.symm (v 4) := by
    obtain ⟨p,hp,he⟩ := hle (mem_map_of_mem (MulAut.conj u).toMonoidHom ha)
    change (MulAut.conj v) p = (MulAut.conj u) a at he
    have hye : (MulAut.conj u) a ∈ alternatingGroup (Fin 6) :=
      (inferInstance : (alternatingGroup (Fin 6)).Normal).conj_mem a ha.2 u
    have hpe : p ∈ alternatingGroup (Fin 6) := by
      rw [←he] at hye
      have hh := (inferInstance : (alternatingGroup (Fin 6)).Normal).conj_mem _ hye v⁻¹
      simpa only [MulEquiv.coe_toMonoidHom,MulAut.conj_apply,inv_inv,
        inv_mul_cancel_left,mul_inv_cancel_right,mul_assoc,inv_mul_cancel,mul_one] using hh
    have hp4 := (BinaryFlags.mem_K.mp (BinaryFlags.pointCoreEven_le_K ⟨hp,hpe⟩)).1.1
    have hh := congrArg (fun g : S => g (v 4)) he
    change v (p (v.symm (v 4)))=u (a (u.symm (v 4))) at hh
    rw [v.symm_apply_apply,hp4] at hh
    simpa only [u.symm_apply_apply] using congrArg u.symm hh.symm
  have ha := hfix (planeWords 4 1) ((mem_evenPart_iff _).mpr ⟨1,rfl⟩)
  have hb := hfix (planeWords 4 2) ((mem_evenPart_iff _).mpr ⟨2,rfl⟩)
  have cert : ∀ i : Fin 6, planeWords 4 1 i=i → planeWords 4 2 i=i → False := by decide +kernel
  exact cert _ ha hb

end CubeAction
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R}
local notation "S" => Equiv.Perm (Fin 6)
local notation "M" => (L ⊔ R : Subgroup G)
local notation "T" => R.subgroupOf (L ⊔ R)


private theorem cubic_cover_calculation (s : FullSymmetricAction h e hz hn d)
    (u : S) (x : d.overgroup) (ho : orderOf x=3)
    (hx : s.projection x=(MulAut.conj u) BinaryFlags.pairRotation) :
    replacementMoved d ⊓ centralizer ({x} : Set d.overgroup) =
      replacementMoved d ⊓ center d.overgroup ∧
    Nat.card (⁅replacementMoved d,zpowers x⁆ : Subgroup d.overgroup) = 16 ∧
    replacementMoved d = ⁅replacementMoved d,zpowers x⁆ ⊔
      (replacementMoved d ⊓ center d.overgroup) := by
  let U := replacementMoved d
  let f := coverProjection h e hz hn d
  let := replacementMoved_normal h d
  have hfixed : U ⊓ centralizer ({x} : Set d.overgroup) = U ⊓ center d.overgroup := by
    apply le_antisymm
    · rintro a ⟨ha,hac⟩
      refine ⟨ha,?_⟩
      have he := s.cover_conjugate x ⟨a,ha⟩ ⟨a,ha⟩ (by
        rw [←mem_centralizer_singleton_iff.mp hac,mul_inv_cancel_right])
      rw [hx] at he
      have hzero := CubeAction.natural_conjugate_fixed_zero u _ he.symm
      have hk : (⟨a,ha⟩ : U) ∈ f.ker := by
        change f ⟨a,ha⟩=1
        exact Multiplicative.toAdd.injective hzero
      rw [show f = coverProjection h e hz hn d from rfl,coverProjection_kernel_center s] at hk
      exact hk
    · exact inf_le_inf_left U (center_le_centralizer _)
  have hU := IsElementaryAbelian.isPGroup 2 U
  have hnorm : x ∈ normalizer (U : Set d.overgroup) := by
    rw [normalizer_eq_top]; trivial
  have hcop : Nat.Coprime (Nat.card (zpowers x)) (Nat.card U) := by
    obtain ⟨n,hn⟩ := hU.exists_card_eq
    rw [Nat.card_zpowers,ho,hn]
    exact Nat.Coprime.pow_right n (by decide)
  have hC : Nat.card (U ⊓ center d.overgroup : Subgroup d.overgroup) = Nat.card f.ker := by
    have hm : f.ker.map U.subtype=U ⊓ center d.overgroup := by
      rw [show f = coverProjection h e hz hn d from rfl,coverProjection_kernel_center s,
        map_comap_eq,range_subtype,inf_comm]
    rw [←hm,card_map_of_injective U.subtype_injective]
  have hr : Nat.card f.range=16 := by
    rw [MonoidHom.range_eq_top.mpr (coverProjection_surjective h e hz hn d),
      Nat.card_congr (topEquiv).toEquiv]
    change Nat.card (BinaryPermutation.natural (Fin 6))=16
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),
      BinaryPermutation.finrank_natural_even (Fin 6) (by decide)]
    norm_num
  have hprod := f.ker.card_mul_index
  rw [index_ker,hr] at hprod
  have hprod' := commutator_card_mul_centralizer_card U (zpowers x) (zpowers_le.mpr hnorm) hcop
  have hcent : centralizer (zpowers x : Set d.overgroup) =
      centralizer ({x} : Set d.overgroup) := by rw [zpowers_eq_closure,centralizer_closure]
  rw [hcent,hfixed,hC] at hprod'
  change Nat.card f.ker * 16 = Nat.card U at hprod
  have hpos := Nat.card_pos (α := f.ker)
  refine ⟨hfixed,?_,?_⟩
  · change Nat.card (⁅U,zpowers x⁆ : Subgroup d.overgroup)=16
    nlinarith
  · rw [←hfixed]
    exact CubeAction.cubic_decomposition U hU x ho hnorm

/-- The cubic in the actual radical normalizer moves the same even plane
in both the radical and its Thompson subgroup. Its actual fixed subgroup
maps onto the diagonal line, and its commutators have the stated literal
core supplements. No splitting of the radical or moved cover is asserted. -/
theorem nonsylow_cube_cubic_action_knownSimple
    (hb : 2 < replacementDistance h d)
    (hns : ¬ ∃ P : Sylow 2 M, (P : Subgroup M) = T)
    (u : S) (himage : d.radical.map (SourceReduction.projection h e hz hn d) =
      (D 6).map (MulAut.conj u).toMonoidHom) :
    ∃ x : d.overgroup, x ∈ normalizer (d.radical : Set d.overgroup) ∧
      orderOf x=3 ∧ SourceReduction.projection h e hz hn d x =
        (MulAut.conj u) BinaryFlags.pairRotation ∧
      (⁅d.radical,zpowers x⁆ : Subgroup d.overgroup).map
        (SourceReduction.projection h e hz hn d) =
          (evenPart 6).map (MulAut.conj u).toMonoidHom ∧
      (⁅Stellmacher.elementaryAbelianMaxJ d.radical,zpowers x⁆ : Subgroup d.overgroup).map
        (SourceReduction.projection h e hz hn d) =
          (evenPart 6).map (MulAut.conj u).toMonoidHom ∧
      pCore 2 d.overgroup ⊔ ⁅d.radical,zpowers x⁆ =
        d.radical ⊓ (alternatingGroup (Fin 6)).comap (SourceReduction.projection h e hz hn d) ∧
      pCore 2 d.overgroup ⊔ ⁅Stellmacher.elementaryAbelianMaxJ d.radical,zpowers x⁆ =
        d.radical ⊓ (alternatingGroup (Fin 6)).comap (SourceReduction.projection h e hz hn d) ∧
      (d.radical ⊓ centralizer ({x} : Set d.overgroup)).map
        (SourceReduction.projection h e hz hn d) =
          (zpowers (dWords 7)).map (MulAut.conj u).toMonoidHom ∧
      d.radical = ⁅d.radical,zpowers x⁆ ⊔
        (d.radical ⊓ centralizer ({x} : Set d.overgroup)) := by
  obtain ⟨x,hx,ho,hqx⟩ := nonsylow_cube_cubic_knownSimple hb hns u himage
  let q := SourceReduction.projection h e hz hn d
  have hm := CubeAction.moved_image q d.radical x u hqx (Or.inr himage)
  have hJ := CubeAction.moved_image q (Stellmacher.elementaryAbelianMaxJ d.radical) x u hqx
    (large_distance_cube_thompson_knownSimple hb u himage)
  have hk : q.ker ≤ d.radical := by
    rw [show q = SourceReduction.projection h e hz hn d from rfl,SourceReduction.projection_kernel]
    exact replacement_core_le_radical h d
  refine ⟨x,hx,ho,hqx,hm,hJ,?_,?_,
    CubeAction.cubic_fixed_image q d.radical (replacement_radical_isPGroup h d) x ho hx u hqx himage,
    CubeAction.cubic_decomposition d.radical (replacement_radical_isPGroup h d) x ho hx⟩
  · exact (SourceReduction.projection_kernel h e hz hn d) ▸
      CubeAction.even_pullback q d.radical hk u himage _ hm
  · exact (SourceReduction.projection_kernel h e hz hn d) ▸
      CubeAction.even_pullback q d.radical hk u himage _ hJ

/-- Beyond four, the same cubic lies in the original MS2(a) witness and
has the exact fixed and moved images on the original nonsylow radical.
The original core supplement and the replacement Thompson supplement
use the original and restricted canonical projections respectively. -/
theorem nonsylow_four_lt_original_cubic_action_knownSimple
    (hb : 4 < replacementDistance h d)
    (hns : ¬ ∃ P : Sylow 2 M, (P : Subgroup M) = T)
    (H : Subgroup M) (hodd : Odd H.index) (hcore : H.pCoreIn 2=T) :
    H.index=15 ∧ ∃ u : S, ∃ x : d.overgroup,
      (x : M) ∈ H ∧ orderOf x=3 ∧
      OriginalRadical.ambientProjection h e hz hn (x : M) =
        (MulAut.conj u) BinaryFlags.pairRotation ∧
      (⁅T,zpowers (x : M)⁆ : Subgroup M).map
        (OriginalRadical.ambientProjection h e hz hn) =
          (evenPart 6).map (MulAut.conj u).toMonoidHom ∧
      pCore 2 M ⊔ ⁅T,zpowers (x : M)⁆ = T ⊓
        (alternatingGroup (Fin 6)).comap (OriginalRadical.ambientProjection h e hz hn) ∧
      (T ⊓ centralizer ({(x : M)} : Set M)).map
        (OriginalRadical.ambientProjection h e hz hn) =
          (zpowers (dWords 7)).map (MulAut.conj u).toMonoidHom ∧
      T = ⁅T,zpowers (x : M)⁆ ⊔ (T ⊓ centralizer ({(x : M)} : Set M)) ∧
      pCore 2 d.overgroup ⊔ ⁅Stellmacher.elementaryAbelianMaxJ d.radical,zpowers x⁆ =
        d.radical ⊓ (alternatingGroup (Fin 6)).comap (SourceReduction.projection h e hz hn d) ∧
      replacementMoved d ⊓ centralizer ({x} : Set d.overgroup) =
        replacementMoved d ⊓ center d.overgroup ∧
      Nat.card (⁅replacementMoved d,zpowers x⁆ : Subgroup d.overgroup) = 16 ∧
      replacementMoved d = ⁅replacementMoved d,zpowers x⁆ ⊔
        (replacementMoved d ⊓ center d.overgroup) := by
  have hb2 : 2 < replacementDistance h d := by omega
  obtain ⟨u,hu⟩ := nonsylow_four_lt_radical_image_cube_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hns
  obtain ⟨hH,hi,hrestrict⟩ := nonsylow_cube_original_witness_knownSimple hb2 hns u hu H hodd hcore
  obtain ⟨x,hx,ho,hqx,_,_,_,hJ,_,_⟩ := nonsylow_cube_cubic_action_knownSimple hb2 hns u hu
  have hxH : (x : M) ∈ H := by
    change x ∈ H.subgroupOf d.overgroup
    rwa [hrestrict]
  have hxN : (x : M) ∈ normalizer (T : Set M) := hH ▸ hxH
  let q := OriginalRadical.ambientProjection h e hz hn
  have hox : orderOf (x : M) = 3 := by
    exact (orderOf_injective d.overgroup.subtype d.overgroup.subtype_injective x).trans ho
  have hqx' : q (x : M)=(MulAut.conj u) BinaryFlags.pairRotation := by
    have he := congrArg (fun f : d.overgroup →* S => f x)
      (OriginalRadical.ambientProjection_restriction h e hz hn d)
    exact he.trans hqx
  have hTq : (T).map q=(D 6).map (MulAut.conj u).toMonoidHom := by
    exact (OriginalRadical.nonsylow_radical_image (e := e) (hz := hz) (hn := hn) hb2 hns).trans hu
  have hk : q.ker ≤ T := by
    rw [show q = OriginalRadical.ambientProjection h e hz hn from rfl,
      OriginalRadical.ambientProjection_kernel]
    exact h.relative_radical.twoCore_le
  have hm := CubeAction.moved_image q T (x : M) u hqx' (Or.inr hTq)
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hsx : s.projection x=(MulAut.conj u) BinaryFlags.pairRotation := by
    rw [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s]
    exact hqx
  have hc := cubic_cover_calculation s u x ho hsx
  refine ⟨hi,u,x,hxH,ho,hqx',hm,?_,
    CubeAction.cubic_fixed_image q T h.relative_radical.isPGroup (x : M) hox hxN u hqx' hTq,
    CubeAction.cubic_decomposition T h.relative_radical.isPGroup (x : M) hox hxN,hJ,hc⟩
  exact (OriginalRadical.ambientProjection_kernel h e hz hn) ▸
    CubeAction.even_pullback q T hk u hTq _ hm

/-- The actual Thompson image in the three-pair branch lies in no point
core. This obstructs the point-core containment in the MS93 (5.10) route;
the corresponding shifted-path geometric premise is still required. -/
theorem large_distance_cube_thompson_not_point_knownSimple
    (hb : 2 < replacementDistance h d) (u : S)
    (himage : d.radical.map (SourceReduction.projection h e hz hn d) =
      (D 6).map (MulAut.conj u).toMonoidHom) (v : S) :
    ¬ (Stellmacher.elementaryAbelianMaxJ d.radical).map
        (SourceReduction.projection h e hz hn d) ≤
      BinaryFlags.pointCore.map (MulAut.conj v).toMonoidHom := by
  intro hle
  apply CubeAction.even_not_point u v
  rcases large_distance_cube_thompson_knownSimple hb u himage with hJ | hJ
  · exact hJ ▸ hle
  · exact (map_mono (show evenPart 6 ≤ D 6 from inf_le_left)).trans (hJ ▸ hle)


end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
