module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource.Small
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.SourceSetup.BinaryCoefficients
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryAbelian.Block
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Transport

/-!
# The actual binary abelian branch of the original rank-one source

Construct the binary MS input inside the literal outside group I. The source
natural quotient has one or two copies. The one-copy short block retains its
fixed kernel and the two-copy core has trivial kernel; both feed the original
marked-plane exclusions with their actual quotient and inclusion maps.

Source: Aschbacher–Smith C.1.34(1),(2),15.3.31, printed pp.136,1132.
-/
public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource
open ChapterA.Section05To06 RankOneConfiguration EightGeometry.NaturalModule.Recognition SmallExtension SmallExtension.CentralCover
  SmallExtension.CentralCover.LinearThree ChapterC
variable {G : Type*} [Group G] [Finite G] {d : LocalData G} {I : Subgroup G}
  {c : ComponentWitness d I}

private theorem characteristic_map_equiv {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (C : Subgroup A) (hC : C.Characteristic) :
    (C.map e.toMonoidHom).Characteristic := by
  apply characteristic_iff_le_comap.mpr
  intro a x hx
  obtain ⟨y, hy, rfl⟩ := hx
  let b : MulAut A := e.trans (a.trans e.symm)
  exact ⟨b y, (characteristic_iff_le_comap.mp hC b) hy, e.apply_symm_apply _⟩

/-- The original Sylow and characteristic-subgroup hypotheses supply every
binary MS premise at the actual component inside I. -/
def source_binaryMSInput (s : SourceData KnownSimple.IsKnownSimple d c)
    (e : (c.L ⧸ pCore 2 c.L) ≃* SL) :
    BinaryMS.Input KnownSimple.IsKnownSimple (c.L.subgroupOf I) (d.S.subgroupOf I) := by
  have hSI : d.S ≤ I := (Chapter1.isSylowIn_iff.mp ⟨s.sylow,s.sylow_eq⟩).2.1
  let K := c.L.subgroupOf I
  let R := d.S.subgroupOf I
  let eK : K ≃* c.L := subgroupOfEquivOfLe (component_le c)
  let := s.normal
  refine {
    sqtk := s.sqtk
    fitting := s.characteristicTwo
    component := LocalData.thompson_component_in c.le_thompson c.component
    quotientEquiv := (QuotientGroup.congr _ _ eK (pCore_map_iso 2 eK)).trans e
    product := ?_
    radical := ?_
    characteristic := ?_ }
  · intro i
    have hi : i ∈ K ⊔ R := by
      change i ∈ c.L.subgroupOf I ⊔ d.S.subgroupOf I
      rw [← subgroupOf_sup (component_le c) hSI,← s.generated,subgroupOf_self]
      trivial
    exact mem_sup_of_normal_left.mp hi
  · have he : R = (s.sylow : Subgroup I) := by
      apply map_injective I.subtype_injective
      exact (map_subgroupOf_eq_of_le hSI).trans s.sylow_eq.symm
    change MSOddIndexRadical R
    rw [he]
    have hne : (s.sylow : Subgroup I) ≠ ⊤ := by
      intro ht
      have hp : IsPGroup 2 K := s.sylow.isPGroup'.to_le (by rw [ht]; exact le_top)
      let := hp.isNilpotent
      exact (LocalData.thompson_component_in c.le_thompson c.component).not_isSolvable inferInstance
    refine ⟨s.sylow,lt_top_iff_ne_top.mpr hne,?_,?_⟩
    · exact Nat.not_even_iff_odd.mp (by simpa only [even_iff_two_dvd] using s.sylow.not_dvd_index)
    · have ht : pCore 2 (s.sylow : Subgroup I) = ⊤ := by
        apply top_unique
        exact le_sSup ⟨inferInstance,s.sylow.isPGroup'.to_subgroup ⊤⟩
      rw [ht,← MonoidHom.range_eq_map,range_subtype]
  · intro C hC hne hn
    let eR : R ≃* d.S := subgroupOfEquivOfLe hSI
    let D : Subgroup d.S := C.map eR.toMonoidHom
    have hD : D.Characteristic := characteristic_map_equiv eR C hC
    have hDne : D ≠ ⊥ := fun hz => hne ((map_eq_bot_iff_of_injective C eR.injective).mp hz)
    have he : (D.map d.S.subtype).subgroupOf I = C.map R.subtype := by
      apply map_injective I.subtype_injective
      rw [map_subgroupOf_eq_of_le ((map_subtype_le D).trans hSI),map_map,map_map]
      rfl
    exact s.characteristic D hD hDne (he.symm ▸ hn)

omit [Finite G] in
private theorem source_binaryCore_map (s : SourceData KnownSimple.IsKnownSimple d c) :
    (BinaryMS.commutatorCore (c.L.subgroupOf I)).map I.subtype = extensionCore c.L := by
  change (⁅pCore 2 I,c.L.subgroupOf I⁆).map I.subtype = _
  rw [map_commutator,map_subgroupOf_eq_of_le (component_le c)]
  change ⁅I.pCoreIn 2,c.L⁆ = extensionCore c.L
  rw [extensionCore_eq_overgroup d c s.contains s.normal]

private def source_binaryCore_equiv (s : SourceData KnownSimple.IsKnownSimple d c) :
    BinaryMS.commutatorCore (c.L.subgroupOf I) ≃* extensionCore c.L :=
  ((BinaryMS.commutatorCore (c.L.subgroupOf I)).equivMapOfInjective I.subtype
    I.subtype_injective).trans (MulEquiv.subgroupCongr (source_binaryCore_map s))

private def pairCoordinates : (Fin 2 → Space) ≃ₗ[ZMod 2] (Space × Space) where
  toFun v := (v 0,v 1)
  invFun v := ![v.1,v.2]
  left_inv v := by ext i; fin_cases i <;> rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The actual binary quotient and abelian commutator core suffice for the
source31 contradiction; no universal MS classification or pure one-copy core
is assumed. -/
theorem source_binary_abelian_false (s : SourceData KnownSimple.IsKnownSimple d c)
    (hm : Parabolics.SmallParabolicMarking d I c.L)
    (e : (c.L ⧸ pCore 2 c.L) ≃* SL)
    (hQ : IsMulCommutative (extensionCore c.L)) : False := by
  let h := source_binaryMSInput s e
  let eQ := source_binaryCore_equiv s
  have hc : IsMulCommutative (BinaryMS.commutatorCore (c.L.subgroupOf I)) :=
    isMulCommutative_iff.mpr (fun x y => eQ.injective (by
      rw [map_mul,map_mul]; exact isMulCommutative_iff.mp hQ _ _))
  let : IsSimpleGroup Matrix.PSL3Two.PSL := Atlas.psl_simple_high_rank 3 (by decide)
  let : IsSimpleGroup (c.L ⧸ pCore 2 c.L) := (e.trans Matrix.PSL3Two.equiv).isSimpleGroup
  obtain ⟨m,hmul,⟨q⟩⟩ := BinaryMS.AbelianCore.QuotientRecognition.Input.exists_abelianCore_naturalQuotient
    (h := h) hc
  let eK : c.L.subgroupOf I ≃* c.L := subgroupOfEquivOfLe (component_le c)
  rcases hmul with rfl | rfl
  · let bm : BlockModuleModel (c.L.subgroupOf I) (BlockModels.multiplicativeAction natural) := {
      quotientIso := q.quotientEquiv
      moduleIso := q.singleModuleEquiv
      intertwining := by
        intro l x
        rw [q.singleModuleEquiv_mk,q.singleModuleEquiv_mk]
        exact congrArg Multiplicative.ofAdd (q.singleProjection_conjugate l x) }
    exact s.binary_natural_short_false hm ((q.block_short hc).of_mulEquiv eK)
      (bm.comap eK.symm)
  · have hk := h.abelianCore_fixedKernel_eq_one_of_twoCopies hc q
    have hbot : BinaryMS.coreFixed (c.L.subgroupOf I) = ⊥ := Subgroup.card_eq_one.mp hk
    have hi : Function.Injective q.projection := by
      rw [← MonoidHom.ker_eq_bot_iff,q.kernel,hbot]
    let f := MulEquiv.ofBijective q.projection ⟨hi,q.surjective⟩
    let a := (QuotientGroup.congr _ _ eK.symm (pCore_map_iso 2 eK.symm)).trans q.quotientEquiv
    let model : LinearModels.AbelianCore c.L (natural.prod natural) := {
      quotientIso := a
      equiv := eQ.symm.trans (f.trans pairCoordinates.toAddEquiv.toMultiplicative)
      action := by
        intro l x y hxy
        have he : eQ.symm y = h.coreConjugate (eK.symm l) (eQ.symm x) := by
          apply Subtype.ext
          apply Subtype.ext
          have hval (z : extensionCore c.L) : ((eQ.symm z : I) : G) = z :=
            congrArg Subtype.val (eQ.apply_symm_apply z)
          rw [h.coreConjugate_val]
          change ((eQ.symm y : I) : G) = (l : G) * ((eQ.symm x : I) : G) * (l : G)⁻¹
          rw [hval,hval]
          exact hxy
        change Multiplicative.ofAdd (pairCoordinates (q.projection (eQ.symm y)).toAdd) = _
        rw [he]
        apply congrArg Multiplicative.ofAdd
        apply Prod.ext
        · exact q.equivariant (eK.symm l) (eQ.symm x) 0
        · exact q.equivariant (eK.symm l) (eQ.symm x) 1 }
    exact s.binary_double_abelian_false hm model

/-- The binary abelian case of15.3.31 at the literal original local datum. -/
theorem source_lemma_15_3_31_abelian_binary
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    (hshadow : SymmetricThreeShadow d.Yplus d.S)
    {I : Subgroup G} (hI : I ∈ d.HplusMinimal) (hf : HasCharacteristicTwo I)
    (c : ComponentWitness d I) (hm : Parabolics.SmallParabolicMarking d I c.L)
    (e : (c.L ⧸ pCore 2 c.L) ≃* SL)
    (hQ : IsMulCommutative (extensionCore c.L)) : False := by
  obtain ⟨s⟩ := source_smallData hG d hempty hM hu hmany hshadow hI hf c
  exact source_binary_abelian_false s hm e hQ

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource
